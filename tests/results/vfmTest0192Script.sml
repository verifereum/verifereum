Theory vfmTest0192[no_sig_docs]
Ancestors vfmTestDefs0192
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0192_0.nsv", "result0192_1.nsv", "result0192_2.nsv", "result0192_3.nsv"];
val thyn = "vfmTestDefs0192";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
