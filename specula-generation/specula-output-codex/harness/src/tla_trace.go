// Copyright IBM Corp. All Rights Reserved.
//
// SPDX-License-Identifier: Apache-2.0
//

package bft

import (
	"encoding/json"
	"fmt"
	"os"
	"path/filepath"
	"sort"
	"strconv"
	"sync"
	"time"

	"github.com/hyperledger-labs/SmartBFT/pkg/types"
	protos "github.com/hyperledger-labs/SmartBFT/smartbftprotos"
	"google.golang.org/protobuf/proto"
)

var tlaTrace = &tlaTraceSink{
	values:    make(map[string]string),
	delivered: make(map[string]map[uint64]struct{}),
	walLen:    make(map[string]int),
	syncLock:  "Nil",
}

type tlaTraceSink struct {
	lock      sync.Mutex
	file      *os.File
	enabled   bool
	init      bool
	nextValue int
	values    map[string]string
	delivered map[string]map[uint64]struct{}
	walLen    map[string]int
	syncLock  string
}

func (t *tlaTraceSink) initialize() {
	if t.init {
		return
	}
	t.init = true
	if os.Getenv("SMARTBFT_TLA_TRACE") == "" {
		return
	}
	path := os.Getenv("SMARTBFT_TLA_TRACE_FILE")
	if path == "" {
		dir := os.Getenv("TRACE_DIR")
		if dir == "" {
			dir = "traces"
		}
		path = filepath.Join(dir, "smartbft.ndjson")
	}
	if err := os.MkdirAll(filepath.Dir(path), 0o755); err != nil {
		return
	}
	f, err := os.OpenFile(path, os.O_CREATE|os.O_WRONLY|os.O_APPEND, 0o644)
	if err != nil {
		return
	}
	t.file = f
	t.enabled = true
}

func tlaNodeID(id uint64) string {
	if id == 0 {
		return "Nil"
	}
	return "s" + strconv.FormatUint(id, 10)
}

func tlaPhaseName(phase Phase) string {
	switch phase {
	case COMMITTED:
		return "PhaseCommitted"
	case PROPOSED:
		return "PhaseProposed"
	case PREPARED:
		return "PhasePrepared"
	case ABORT:
		return "PhaseAbort"
	default:
		return "PhaseCommitted"
	}
}

func tlaProposalMetadata(prop types.Proposal) *protos.ViewMetadata {
	md := &protos.ViewMetadata{}
	if len(prop.Metadata) == 0 {
		return md
	}
	if err := proto.Unmarshal(prop.Metadata, md); err != nil {
		return &protos.ViewMetadata{}
	}
	return md
}

func tlaProtoProposalMetadata(prop *protos.Proposal) *protos.ViewMetadata {
	md := &protos.ViewMetadata{}
	if prop == nil || len(prop.Metadata) == 0 {
		return md
	}
	if err := proto.Unmarshal(prop.Metadata, md); err != nil {
		return &protos.ViewMetadata{}
	}
	return md
}

func tlaCheckpointSeq(prop *protos.Proposal) uint64 {
	return tlaProtoProposalMetadata(prop).LatestSequence
}

func tlaProposalValue(prop types.Proposal) string {
	tlaTrace.lock.Lock()
	defer tlaTrace.lock.Unlock()
	return tlaTrace.proposalValueLocked(prop.Digest())
}

func tlaProtoProposalValue(prop *protos.Proposal) string {
	if prop == nil {
		return "Genesis"
	}
	p := types.Proposal{
		VerificationSequence: int64(prop.VerificationSequence),
		Header:               prop.Header,
		Payload:              prop.Payload,
		Metadata:             prop.Metadata,
	}
	return tlaProposalValue(p)
}

func (t *tlaTraceSink) proposalValueLocked(digest string) string {
	if digest == "" {
		return "Genesis"
	}
	if v, exists := t.values[digest]; exists {
		return v
	}
	t.nextValue++
	if t.nextValue > 2 {
		t.nextValue = 2
	}
	v := fmt.Sprintf("v%d", t.nextValue)
	t.values[digest] = v
	return v
}

func tlaMarkDelivered(node string, seq uint64) {
	tlaTrace.lock.Lock()
	defer tlaTrace.lock.Unlock()
	if tlaTrace.delivered[node] == nil {
		tlaTrace.delivered[node] = make(map[uint64]struct{})
	}
	tlaTrace.delivered[node][seq] = struct{}{}
}

func tlaIncWal(node string) {
	tlaTrace.lock.Lock()
	defer tlaTrace.lock.Unlock()
	tlaTrace.walLen[node]++
}

func tlaSetSyncLock(node string) {
	tlaTrace.lock.Lock()
	defer tlaTrace.lock.Unlock()
	tlaTrace.syncLock = node
}

func tlaClearSyncLock() {
	tlaTrace.lock.Lock()
	defer tlaTrace.lock.Unlock()
	tlaTrace.syncLock = "Nil"
}

func tlaDeliveredListLocked(node string) []uint64 {
	out := make([]uint64, 0, len(tlaTrace.delivered[node]))
	for seq := range tlaTrace.delivered[node] {
		out = append(out, seq)
	}
	sort.Slice(out, func(i, j int) bool { return out[i] < out[j] })
	return out
}

func tlaEmit(event, node string, state map[string]interface{}, fields map[string]interface{}) {
	tlaTrace.lock.Lock()
	defer tlaTrace.lock.Unlock()
	tlaTrace.initialize()
	if !tlaTrace.enabled {
		return
	}
	if state == nil {
		state = make(map[string]interface{})
	}
	state["delivered"] = tlaDeliveredListLocked(node)
	if _, exists := state["wal_len"]; !exists {
		state["wal_len"] = tlaTrace.walLen[node]
	}
	state["sync_lock_holder"] = tlaTrace.syncLock
	state["crashed"] = false
	line := map[string]interface{}{
		"tag":   "trace",
		"ts":    time.Now().UnixNano(),
		"event": event,
		"node":  node,
		"state": state,
	}
	for k, v := range fields {
		line[k] = v
	}
	_ = json.NewEncoder(tlaTrace.file).Encode(line)
	_ = tlaTrace.file.Sync()
}

func tlaControllerState(c *Controller, phaseName string) map[string]interface{} {
	node := tlaNodeID(c.ID)
	seq := uint64(0)
	if c.ViewSequences != nil {
		if vs := c.ViewSequences.Load(); vs != nil {
			seq = vs.(ViewSequence).ProposalSeq
		}
	}
	if seq == 0 {
		seq = c.latestSeq() + 1
	}
	if phaseName == "" {
		phaseName = "PhaseCommitted"
		c.currViewLock.RLock()
		if view, ok := c.currView.(*View); ok && view != nil {
			phaseName = tlaPhaseName(view.Phase)
		}
		c.currViewLock.RUnlock()
	}
	prop, _ := c.Checkpoint.Get()
	return map[string]interface{}{
		"view":              c.getCurrentViewNumber(),
		"proposal_seq":      seq,
		"decisions_in_view": c.getCurrentDecisionsInView(),
		"checkpoint_seq":    tlaCheckpointSeq(prop),
		"phase":             phaseName,
		"wal_len":           tlaTrace.walLen[node],
		"viewdata_count":    0,
	}
}

func tlaTraceController(c *Controller, event string, fields map[string]interface{}) {
	tlaEmit(event, tlaNodeID(c.ID), tlaControllerState(c, ""), fields)
}

func tlaTraceControllerDecision(c *Controller, proposal types.Proposal) {
	md := tlaProposalMetadata(proposal)
	tlaMarkDelivered(tlaNodeID(c.ID), md.LatestSequence)
	tlaEmit("controller_decide", tlaNodeID(c.ID), tlaControllerState(c, "PhaseCommitted"), map[string]interface{}{
		"value": tlaProposalValue(proposal),
	})
}

func tlaTraceMutuallyExclusiveDeliver(c *Controller, proposal types.Proposal, delivered bool) {
	md := tlaProposalMetadata(proposal)
	if delivered {
		tlaMarkDelivered(tlaNodeID(c.ID), md.LatestSequence)
	}
	tlaEmit("mutually_exclusive_deliver", tlaNodeID(c.ID), tlaControllerState(c, "PhaseCommitted"), map[string]interface{}{
		"value": tlaProposalValue(proposal),
	})
}

func tlaTraceControllerSyncBegin(c *Controller) {
	node := tlaNodeID(c.ID)
	tlaSetSyncLock(node)
	tlaEmit("controller_sync_begin", node, tlaControllerState(c, ""), map[string]interface{}{
		"sync_lock_holder": node,
	})
}

func tlaTraceControllerSyncApply(c *Controller, view, seq, decisions uint64) {
	tlaClearSyncLock()
	tlaEmit("controller_sync_apply", tlaNodeID(c.ID), tlaControllerState(c, ""), map[string]interface{}{
		"sync_view":      view,
		"sync_seq":       seq,
		"sync_decisions": decisions,
	})
}

func tlaViewState(v *View, phaseName string) map[string]interface{} {
	if phaseName == "" {
		phaseName = tlaPhaseName(v.Phase)
	}
	return map[string]interface{}{
		"view":              v.Number,
		"proposal_seq":      v.ProposalSequence,
		"decisions_in_view": v.DecisionsInView,
		"checkpoint_seq":    0,
		"phase":             phaseName,
		"wal_len":           tlaTrace.walLen[tlaNodeID(v.SelfID)],
		"viewdata_count":    0,
	}
}

func tlaTraceView(v *View, event string, proposal *types.Proposal, phaseName string) {
	fields := map[string]interface{}{}
	if proposal != nil {
		fields["value"] = tlaProposalValue(*proposal)
	}
	tlaEmit(event, tlaNodeID(v.SelfID), tlaViewState(v, phaseName), fields)
}

func tlaViewChangerState(v *ViewChanger, phaseName string) map[string]interface{} {
	if phaseName == "" {
		phaseName = "PhaseCommitted"
	}
	seq, _ := v.extractCurrentSequence()
	return map[string]interface{}{
		"view":              v.currView,
		"proposal_seq":      seq + 1,
		"decisions_in_view": 0,
		"checkpoint_seq":    seq,
		"phase":             phaseName,
		"wal_len":           tlaTrace.walLen[tlaNodeID(v.SelfID)],
		"viewdata_count":    len(v.viewDataMsgs.voted),
	}
}

func tlaTraceViewChanger(v *ViewChanger, event string, fields map[string]interface{}, phaseName string) {
	tlaEmit(event, tlaNodeID(v.SelfID), tlaViewChangerState(v, phaseName), fields)
}

func tlaTraceViewData(v *ViewChanger, sender uint64, svd *protos.SignedViewData) {
	vd := &protos.ViewData{}
	_ = proto.Unmarshal(svd.RawViewData, vd)
	fields := map[string]interface{}{
		"sender":         tlaNodeID(sender),
		"prepared":       vd.InFlightPrepared,
		"has_inflight":   vd.InFlightProposal != nil,
		"proposal_valid": true,
	}
	if vd.InFlightProposal != nil {
		fields["value"] = tlaProtoProposalValue(vd.InFlightProposal)
	}
	tlaTraceViewChanger(v, "viewchanger_accept_viewdata", fields, "PhaseAbort")
}

func tlaTraceRecover(v *View) {
	tlaEmit("recover", tlaNodeID(v.SelfID), tlaViewState(v, tlaPhaseName(v.Phase)), map[string]interface{}{
		"crashed": false,
	})
}
