Theory vfmTest3159[no_sig_docs]
Ancestors vfmTestDefs3159
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result3159_0.nsv", "result3159_1.nsv"];
val thyn = "vfmTestDefs3159";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
