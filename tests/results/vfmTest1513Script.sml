Theory vfmTest1513[no_sig_docs]
Ancestors vfmTestDefs1513
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1513_0.nsv", "result1513_1.nsv", "result1513_2.nsv", "result1513_3.nsv", "result1513_4.nsv", "result1513_5.nsv", "result1513_6.nsv", "result1513_7.nsv"];
val thyn = "vfmTestDefs1513";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
