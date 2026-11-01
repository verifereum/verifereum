Theory vfmTest1476[no_sig_docs]
Ancestors vfmTestDefs1476
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1476_0.nsv", "result1476_1.nsv", "result1476_2.nsv", "result1476_3.nsv", "result1476_4.nsv", "result1476_5.nsv", "result1476_6.nsv", "result1476_7.nsv", "result1476_8.nsv", "result1476_9.nsv", "result1476_10.nsv", "result1476_11.nsv"];
val thyn = "vfmTestDefs1476";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
