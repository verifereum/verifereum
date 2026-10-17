Theory vfmTest0621[no_sig_docs]
Ancestors vfmTestDefs0621
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0621_0.nsv", "result0621_1.nsv", "result0621_2.nsv", "result0621_3.nsv", "result0621_4.nsv", "result0621_5.nsv", "result0621_6.nsv", "result0621_7.nsv", "result0621_8.nsv", "result0621_9.nsv", "result0621_10.nsv", "result0621_11.nsv", "result0621_12.nsv", "result0621_13.nsv", "result0621_14.nsv", "result0621_15.nsv", "result0621_16.nsv", "result0621_17.nsv", "result0621_18.nsv", "result0621_19.nsv", "result0621_20.nsv", "result0621_21.nsv", "result0621_22.nsv", "result0621_23.nsv"];
val thyn = "vfmTestDefs0621";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
