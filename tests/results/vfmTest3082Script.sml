Theory vfmTest3082[no_sig_docs]
Ancestors vfmTestDefs3082
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result3082_0.nsv"];
val thyn = "vfmTestDefs3082";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
