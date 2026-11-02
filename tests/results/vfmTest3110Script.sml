Theory vfmTest3110[no_sig_docs]
Ancestors vfmTestDefs3110
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result3110_0.nsv", "result3110_1.nsv", "result3110_2.nsv", "result3110_3.nsv", "result3110_4.nsv"];
val thyn = "vfmTestDefs3110";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
