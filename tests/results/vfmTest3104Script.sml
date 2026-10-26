Theory vfmTest3104[no_sig_docs]
Ancestors vfmTestDefs3104
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result3104_0.nsv"];
val thyn = "vfmTestDefs3104";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
