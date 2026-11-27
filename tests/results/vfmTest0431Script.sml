Theory vfmTest0431[no_sig_docs]
Ancestors vfmTestDefs0431
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0431_0.nsv", "result0431_1.nsv", "result0431_2.nsv", "result0431_3.nsv"];
val thyn = "vfmTestDefs0431";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
