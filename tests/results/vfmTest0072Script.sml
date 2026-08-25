Theory vfmTest0072[no_sig_docs]
Ancestors vfmTestDefs0072
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0072_0.nsv", "result0072_1.nsv", "result0072_2.nsv", "result0072_3.nsv"];
val thyn = "vfmTestDefs0072";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
