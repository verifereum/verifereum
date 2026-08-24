Theory vfmTest0115[no_sig_docs]
Ancestors vfmTestDefs0115
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0115_0.nsv", "result0115_1.nsv", "result0115_2.nsv", "result0115_3.nsv", "result0115_4.nsv", "result0115_5.nsv", "result0115_6.nsv", "result0115_7.nsv", "result0115_8.nsv", "result0115_9.nsv", "result0115_10.nsv", "result0115_11.nsv", "result0115_12.nsv", "result0115_13.nsv", "result0115_14.nsv", "result0115_15.nsv", "result0115_16.nsv", "result0115_17.nsv", "result0115_18.nsv", "result0115_19.nsv", "result0115_20.nsv", "result0115_21.nsv", "result0115_22.nsv", "result0115_23.nsv"];
val thyn = "vfmTestDefs0115";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
