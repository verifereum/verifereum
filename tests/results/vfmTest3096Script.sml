Theory vfmTest3096[no_sig_docs]
Ancestors vfmTestDefs3096
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result3096_0.nsv", "result3096_1.nsv"];
val thyn = "vfmTestDefs3096";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
