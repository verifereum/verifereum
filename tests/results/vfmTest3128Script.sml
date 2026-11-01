Theory vfmTest3128[no_sig_docs]
Ancestors vfmTestDefs3128
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result3128_0.nsv", "result3128_1.nsv"];
val thyn = "vfmTestDefs3128";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
