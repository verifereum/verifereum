Theory vfmTest0515[no_sig_docs]
Ancestors vfmTestDefs0515
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0515_0.nsv", "result0515_1.nsv", "result0515_2.nsv", "result0515_3.nsv", "result0515_4.nsv", "result0515_5.nsv", "result0515_6.nsv", "result0515_7.nsv", "result0515_8.nsv", "result0515_9.nsv", "result0515_10.nsv", "result0515_11.nsv", "result0515_12.nsv", "result0515_13.nsv", "result0515_14.nsv", "result0515_15.nsv", "result0515_16.nsv", "result0515_17.nsv", "result0515_18.nsv", "result0515_19.nsv", "result0515_20.nsv", "result0515_21.nsv", "result0515_22.nsv", "result0515_23.nsv"];
val thyn = "vfmTestDefs0515";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
