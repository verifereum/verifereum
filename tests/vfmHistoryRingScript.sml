Theory vfmHistoryRing
Ancestors vfmCompute
Libs wordsLib cv_transLib

(* Concrete block inputs for the two independent system-contract rings. *)
Definition history_ring_block_def:
  history_ring_block number timestamp = <|
    baseFeePerGas := 0; excessBlobGas := 0; gasUsed := 0; blobGasUsed := 0;
    number := number; timeStamp := timestamp; coinBase := 0w;
    gasLimit := 30000000; prevRandao := 0w; hash := 0w; rlpSize := 0;
    parentBeaconBlockRoot := 7w; requestsHash := 0w;
    blockAccessListHash := 0w; slotNumber := 0; stateRoot := 0w;
    withdrawalsRoot := 0w; transactions := []; withdrawals := [] |>
End
val () = cv_auto_trans history_ring_block_def;

(* EIP-2935 canonical runtime. Slot 8191 is a sentinel outside its ring. *)
Definition history_ring_accounts_def:
  history_ring_accounts =
    update_account 0x0000F90827F1C53a10cb7A02335B175320002935w
      (empty_account_state with <|
        nonce := 1;
        code := [0x33w;0x73w;0xffw;0xffw;0xffw;0xffw;0xffw;0xffw;
          0xffw;0xffw;0xffw;0xffw;0xffw;0xffw;0xffw;0xffw;0xffw;
          0xffw;0xffw;0xffw;0xffw;0xfew;0x14w;0x60w;0x46w;0x57w;
          0x60w;0x20w;0x36w;0x03w;0x60w;0x42w;0x57w;0x5fw;0x35w;
          0x60w;0x01w;0x43w;0x03w;0x81w;0x11w;0x60w;0x42w;0x57w;
          0x61w;0x1fw;0xffw;0x81w;0x43w;0x03w;0x11w;0x60w;0x42w;
          0x57w;0x61w;0x1fw;0xffw;0x90w;0x06w;0x54w;0x5fw;0x52w;
          0x60w;0x20w;0x5fw;0xf3w;0x5bw;0x5fw;0x5fw;0xfdw;0x5bw;
          0x5fw;0x35w;0x61w;0x1fw;0xffw;0x60w;0x01w;0x43w;0x03w;
          0x06w;0x55w;0x00w];
        storage := update_storage 0w 99w
          (update_storage 1w 98w
            (update_storage 8190w 97w
              (update_storage 8191w 96w empty_storage))) |>)
      empty_accounts
End
val () = cv_auto_trans history_ring_accounts_def;

(* Observe boundary slots of both rings, including the beacon root offset. *)
Definition history_ring_observation_def:
  history_ring_observation hashes number timestamp =
    let accounts = update_beacon_block hashes
      (history_ring_block number timestamp) history_ring_accounts in
    let history = (lookup_account
      0x0000F90827F1C53a10cb7A02335B175320002935w accounts).storage in
    let beacon = (lookup_account
      0x000F3df6D732807Ef1319fB7B8bB8522d0Beac02w accounts).storage in
    (MAP (λslot. lookup_storage slot history) [0w; 1w; 8190w; 8191w],
     MAP (λslot. lookup_storage slot beacon)
       [0w; 1w; 8190w; 8191w; 8192w; 16381w])
End
val () = cv_auto_trans history_ring_observation_def;

Theorem history_ring_first_block:
  history_ring_observation [42w] 1 1 =
    ([42w; 98w; 97w; 96w], [0w; 1w; 0w; 0w; 7w; 0w])
Proof
  CONV_TAC cv_eval
QED

Theorem history_ring_before_wrap:
  history_ring_observation [42w] 8191 8190 =
    ([99w; 98w; 42w; 96w], [0w; 0w; 8190w; 0w; 0w; 7w])
Proof
  CONV_TAC cv_eval
QED

Theorem history_ring_first_wrap:
  history_ring_observation [42w] 8192 8191 =
    ([42w; 98w; 97w; 96w], [8191w; 0w; 0w; 7w; 0w; 0w])
Proof
  CONV_TAC cv_eval
QED

Theorem history_ring_after_wrap:
  history_ring_observation [42w] 8193 8192 =
    ([99w; 42w; 97w; 96w], [0w; 8192w; 0w; 0w; 7w; 0w])
Proof
  CONV_TAC cv_eval
QED

Theorem history_ring_second_wrap:
  history_ring_observation [43w] 16383 16382 =
    ([43w; 98w; 97w; 96w], [16382w; 0w; 0w; 7w; 0w; 0w])
Proof
  CONV_TAC cv_eval
QED

Theorem history_ring_genesis:
  history_ring_observation [42w] 0 8191 =
    ([99w; 98w; 97w; 96w], [8191w; 0w; 0w; 7w; 0w; 0w])
Proof
  CONV_TAC cv_eval
QED

Theorem history_ring_no_parent:
  history_ring_observation [] 8192 8191 =
    ([99w; 98w; 97w; 96w], [8191w; 0w; 0w; 7w; 0w; 0w])
Proof
  CONV_TAC cv_eval
QED
