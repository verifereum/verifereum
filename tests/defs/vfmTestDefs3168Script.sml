Theory vfmTestDefs3168[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/spurious_dragon/eip155_simple_replay_attack_protection/chain_id/legacy_chain_id_over_64_bits.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/spurious_dragon/eip155_simple_replay_attack_protection/chain_id/legacy_chain_id_over_64_bits.json");
val defs = mapi (define_test "3168") tests;
