Theory vfmTest0110[no_sig_docs]
Ancestors vfmTestDefs0110
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0110_0.nsv", "result0110_1.nsv", "result0110_2.nsv", "result0110_3.nsv", "result0110_4.nsv", "result0110_5.nsv", "result0110_6.nsv", "result0110_7.nsv", "result0110_8.nsv", "result0110_9.nsv", "result0110_10.nsv", "result0110_11.nsv", "result0110_12.nsv", "result0110_13.nsv", "result0110_14.nsv", "result0110_15.nsv", "result0110_16.nsv", "result0110_17.nsv"];
val thyn = "vfmTestDefs0110";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
