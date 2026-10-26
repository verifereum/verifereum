Theory vfmTest3033[no_sig_docs]
Ancestors vfmTestDefs3033
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result3033_0.nsv"];
val thyn = "vfmTestDefs3033";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
