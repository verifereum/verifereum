Theory vfmTest2949[no_sig_docs]
Ancestors vfmTestDefs2949
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2949_0.nsv", "result2949_1.nsv", "result2949_2.nsv", "result2949_3.nsv", "result2949_4.nsv", "result2949_5.nsv"];
val thyn = "vfmTestDefs2949";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
