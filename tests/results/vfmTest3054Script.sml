Theory vfmTest3054[no_sig_docs]
Ancestors vfmTestDefs3054
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result3054_0.nsv", "result3054_1.nsv", "result3054_2.nsv", "result3054_3.nsv", "result3054_4.nsv", "result3054_5.nsv"];
val thyn = "vfmTestDefs3054";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
