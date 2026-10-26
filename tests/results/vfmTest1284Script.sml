Theory vfmTest1284[no_sig_docs]
Ancestors vfmTestDefs1284
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1284_0.nsv", "result1284_1.nsv", "result1284_2.nsv", "result1284_3.nsv", "result1284_4.nsv", "result1284_5.nsv", "result1284_6.nsv", "result1284_7.nsv", "result1284_8.nsv"];
val thyn = "vfmTestDefs1284";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
