Theory vfmTest1680[no_sig_docs]
Ancestors vfmTestDefs1680
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1680_0.nsv", "result1680_1.nsv", "result1680_2.nsv", "result1680_3.nsv", "result1680_4.nsv", "result1680_5.nsv", "result1680_6.nsv", "result1680_7.nsv", "result1680_8.nsv"];
val thyn = "vfmTestDefs1680";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
