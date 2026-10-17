Theory vfmTest1664[no_sig_docs]
Ancestors vfmTestDefs1664
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1664_0.nsv", "result1664_1.nsv", "result1664_2.nsv", "result1664_3.nsv", "result1664_4.nsv", "result1664_5.nsv", "result1664_6.nsv", "result1664_7.nsv", "result1664_8.nsv"];
val thyn = "vfmTestDefs1664";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
