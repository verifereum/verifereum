Theory vfmTest2483[no_sig_docs]
Ancestors vfmTestDefs2483
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2483_0.nsv", "result2483_1.nsv", "result2483_2.nsv", "result2483_3.nsv", "result2483_4.nsv", "result2483_5.nsv", "result2483_6.nsv", "result2483_7.nsv", "result2483_8.nsv", "result2483_9.nsv", "result2483_10.nsv", "result2483_11.nsv", "result2483_12.nsv", "result2483_13.nsv", "result2483_14.nsv", "result2483_15.nsv"];
val thyn = "vfmTestDefs2483";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
