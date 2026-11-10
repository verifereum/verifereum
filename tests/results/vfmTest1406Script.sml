Theory vfmTest1406[no_sig_docs]
Ancestors vfmTestDefs1406
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1406_0.nsv", "result1406_1.nsv", "result1406_2.nsv", "result1406_3.nsv", "result1406_4.nsv", "result1406_5.nsv", "result1406_6.nsv", "result1406_7.nsv"];
val thyn = "vfmTestDefs1406";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
