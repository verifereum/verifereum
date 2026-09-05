Theory vfmTest0218[no_sig_docs]
Ancestors vfmTestDefs0218
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0218_0.nsv", "result0218_1.nsv", "result0218_2.nsv", "result0218_3.nsv", "result0218_4.nsv", "result0218_5.nsv", "result0218_6.nsv", "result0218_7.nsv", "result0218_8.nsv", "result0218_9.nsv", "result0218_10.nsv", "result0218_11.nsv", "result0218_12.nsv", "result0218_13.nsv", "result0218_14.nsv", "result0218_15.nsv", "result0218_16.nsv", "result0218_17.nsv", "result0218_18.nsv", "result0218_19.nsv"];
val thyn = "vfmTestDefs0218";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
