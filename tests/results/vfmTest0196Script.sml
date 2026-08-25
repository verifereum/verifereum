Theory vfmTest0196[no_sig_docs]
Ancestors vfmTestDefs0196
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0196_0.nsv", "result0196_1.nsv", "result0196_2.nsv", "result0196_3.nsv", "result0196_4.nsv", "result0196_5.nsv", "result0196_6.nsv", "result0196_7.nsv", "result0196_8.nsv", "result0196_9.nsv", "result0196_10.nsv", "result0196_11.nsv", "result0196_12.nsv", "result0196_13.nsv", "result0196_14.nsv", "result0196_15.nsv", "result0196_16.nsv", "result0196_17.nsv", "result0196_18.nsv", "result0196_19.nsv", "result0196_20.nsv", "result0196_21.nsv", "result0196_22.nsv", "result0196_23.nsv", "result0196_24.nsv", "result0196_25.nsv", "result0196_26.nsv", "result0196_27.nsv", "result0196_28.nsv", "result0196_29.nsv", "result0196_30.nsv", "result0196_31.nsv"];
val thyn = "vfmTestDefs0196";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
