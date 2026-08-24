Theory vfmTest0981[no_sig_docs]
Ancestors vfmTestDefs0981
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0981_0.nsv", "result0981_1.nsv", "result0981_2.nsv", "result0981_3.nsv", "result0981_4.nsv", "result0981_5.nsv", "result0981_6.nsv", "result0981_7.nsv", "result0981_8.nsv", "result0981_9.nsv", "result0981_10.nsv", "result0981_11.nsv", "result0981_12.nsv", "result0981_13.nsv", "result0981_14.nsv", "result0981_15.nsv", "result0981_16.nsv", "result0981_17.nsv", "result0981_18.nsv", "result0981_19.nsv", "result0981_20.nsv", "result0981_21.nsv", "result0981_22.nsv", "result0981_23.nsv", "result0981_24.nsv", "result0981_25.nsv", "result0981_26.nsv", "result0981_27.nsv", "result0981_28.nsv", "result0981_29.nsv", "result0981_30.nsv", "result0981_31.nsv", "result0981_32.nsv", "result0981_33.nsv", "result0981_34.nsv", "result0981_35.nsv"];
val thyn = "vfmTestDefs0981";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
