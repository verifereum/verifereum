Theory vfmTest0244[no_sig_docs]
Ancestors vfmTestDefs0244
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0244_0.nsv", "result0244_1.nsv"];
val thyn = "vfmTestDefs0244";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
