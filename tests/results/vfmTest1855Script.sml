Theory vfmTest1855[no_sig_docs]
Ancestors vfmTestDefs1855
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1855_0.nsv", "result1855_1.nsv", "result1855_2.nsv", "result1855_3.nsv", "result1855_4.nsv", "result1855_5.nsv", "result1855_6.nsv", "result1855_7.nsv", "result1855_8.nsv", "result1855_9.nsv"];
val thyn = "vfmTestDefs1855";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
