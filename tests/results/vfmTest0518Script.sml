Theory vfmTest0518[no_sig_docs]
Ancestors vfmTestDefs0518
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0518_0.nsv"];
val thyn = "vfmTestDefs0518";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
