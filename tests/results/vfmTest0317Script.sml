Theory vfmTest0317[no_sig_docs]
Ancestors vfmTestDefs0317
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0317_0.nsv", "result0317_1.nsv"];
val thyn = "vfmTestDefs0317";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
