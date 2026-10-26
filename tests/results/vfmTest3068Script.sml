Theory vfmTest3068[no_sig_docs]
Ancestors vfmTestDefs3068
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result3068_0.nsv", "result3068_1.nsv"];
val thyn = "vfmTestDefs3068";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
