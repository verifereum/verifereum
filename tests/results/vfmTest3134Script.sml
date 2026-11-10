Theory vfmTest3134[no_sig_docs]
Ancestors vfmTestDefs3134
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result3134_0.nsv"];
val thyn = "vfmTestDefs3134";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
