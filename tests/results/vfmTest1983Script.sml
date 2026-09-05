Theory vfmTest1983[no_sig_docs]
Ancestors vfmTestDefs1983
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1983_0.nsv", "result1983_1.nsv", "result1983_2.nsv", "result1983_3.nsv", "result1983_4.nsv", "result1983_5.nsv", "result1983_6.nsv", "result1983_7.nsv"];
val thyn = "vfmTestDefs1983";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
