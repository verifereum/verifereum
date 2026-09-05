Theory vfmTest0314[no_sig_docs]
Ancestors vfmTestDefs0314
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0314_0.nsv", "result0314_1.nsv"];
val thyn = "vfmTestDefs0314";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
