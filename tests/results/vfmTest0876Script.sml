Theory vfmTest0876[no_sig_docs]
Ancestors vfmTestDefs0876
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0876_0.nsv", "result0876_1.nsv"];
val thyn = "vfmTestDefs0876";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
