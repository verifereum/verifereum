Theory vfmTest0865[no_sig_docs]
Ancestors vfmTestDefs0865
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0865_0.nsv", "result0865_1.nsv"];
val thyn = "vfmTestDefs0865";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
