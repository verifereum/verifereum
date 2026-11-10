Theory vfmTest3040[no_sig_docs]
Ancestors vfmTestDefs3040
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result3040_0.nsv", "result3040_1.nsv"];
val thyn = "vfmTestDefs3040";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
