Theory vfmTest0110[no_sig_docs]
Ancestors vfmTestDefs0110
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0110_0.nsv", "result0110_1.nsv", "result0110_2.nsv", "result0110_3.nsv", "result0110_4.nsv", "result0110_5.nsv"];
val thyn = "vfmTestDefs0110";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
