Theory vfmTest3092[no_sig_docs]
Ancestors vfmTestDefs3092
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result3092_0.nsv", "result3092_1.nsv"];
val thyn = "vfmTestDefs3092";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
