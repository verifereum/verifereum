Theory vfmTest0524[no_sig_docs]
Ancestors vfmTestDefs0524
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0524_0.nsv", "result0524_1.nsv"];
val thyn = "vfmTestDefs0524";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
