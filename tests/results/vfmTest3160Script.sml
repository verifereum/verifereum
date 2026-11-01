Theory vfmTest3160[no_sig_docs]
Ancestors vfmTestDefs3160
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result3160_0.nsv", "result3160_1.nsv"];
val thyn = "vfmTestDefs3160";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
