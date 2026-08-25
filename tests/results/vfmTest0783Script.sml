Theory vfmTest0783[no_sig_docs]
Ancestors vfmTestDefs0783
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0783_0.nsv", "result0783_1.nsv"];
val thyn = "vfmTestDefs0783";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
