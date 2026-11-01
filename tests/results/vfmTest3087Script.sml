Theory vfmTest3087[no_sig_docs]
Ancestors vfmTestDefs3087
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result3087_0.nsv", "result3087_1.nsv"];
val thyn = "vfmTestDefs3087";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
