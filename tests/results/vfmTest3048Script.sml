Theory vfmTest3048[no_sig_docs]
Ancestors vfmTestDefs3048
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result3048_0.nsv", "result3048_1.nsv", "result3048_2.nsv", "result3048_3.nsv", "result3048_4.nsv"];
val thyn = "vfmTestDefs3048";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
