Theory vfmTest3105[no_sig_docs]
Ancestors vfmTestDefs3105
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result3105_0.nsv"];
val thyn = "vfmTestDefs3105";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
