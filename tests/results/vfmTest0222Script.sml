Theory vfmTest0222[no_sig_docs]
Ancestors vfmTestDefs0222
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0222_0.nsv", "result0222_1.nsv", "result0222_2.nsv", "result0222_3.nsv", "result0222_4.nsv", "result0222_5.nsv", "result0222_6.nsv", "result0222_7.nsv", "result0222_8.nsv", "result0222_9.nsv", "result0222_10.nsv", "result0222_11.nsv", "result0222_12.nsv", "result0222_13.nsv", "result0222_14.nsv", "result0222_15.nsv", "result0222_16.nsv", "result0222_17.nsv"];
val thyn = "vfmTestDefs0222";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
