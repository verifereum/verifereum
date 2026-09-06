Theory vfmTest0639[no_sig_docs]
Ancestors vfmTestDefs0639
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0639_0.nsv", "result0639_1.nsv"];
val thyn = "vfmTestDefs0639";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
