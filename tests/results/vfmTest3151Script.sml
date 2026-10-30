Theory vfmTest3151[no_sig_docs]
Ancestors vfmTestDefs3151
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result3151_0.nsv", "result3151_1.nsv", "result3151_2.nsv", "result3151_3.nsv"];
val thyn = "vfmTestDefs3151";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
