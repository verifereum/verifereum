Theory vfmTest1625[no_sig_docs]
Ancestors vfmTestDefs1625
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1625_0.nsv", "result1625_1.nsv", "result1625_2.nsv", "result1625_3.nsv", "result1625_4.nsv", "result1625_5.nsv", "result1625_6.nsv", "result1625_7.nsv"];
val thyn = "vfmTestDefs1625";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
