Theory vfmTest1453[no_sig_docs]
Ancestors vfmTestDefs1453
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1453_0.nsv", "result1453_1.nsv", "result1453_2.nsv", "result1453_3.nsv", "result1453_4.nsv", "result1453_5.nsv", "result1453_6.nsv", "result1453_7.nsv", "result1453_8.nsv", "result1453_9.nsv"];
val thyn = "vfmTestDefs1453";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
