Theory vfmTest3133[no_sig_docs]
Ancestors vfmTestDefs3133
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result3133_0.nsv", "result3133_1.nsv", "result3133_2.nsv", "result3133_3.nsv", "result3133_4.nsv", "result3133_5.nsv", "result3133_6.nsv", "result3133_7.nsv", "result3133_8.nsv"];
val thyn = "vfmTestDefs3133";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
