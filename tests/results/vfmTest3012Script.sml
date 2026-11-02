Theory vfmTest3012[no_sig_docs]
Ancestors vfmTestDefs3012
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result3012_0.nsv"];
val thyn = "vfmTestDefs3012";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
