Theory vfmTest0161[no_sig_docs]
Ancestors vfmTestDefs0161
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0161_0.nsv", "result0161_1.nsv", "result0161_2.nsv", "result0161_3.nsv", "result0161_4.nsv", "result0161_5.nsv", "result0161_6.nsv", "result0161_7.nsv", "result0161_8.nsv", "result0161_9.nsv", "result0161_10.nsv", "result0161_11.nsv", "result0161_12.nsv", "result0161_13.nsv", "result0161_14.nsv", "result0161_15.nsv", "result0161_16.nsv", "result0161_17.nsv", "result0161_18.nsv", "result0161_19.nsv", "result0161_20.nsv", "result0161_21.nsv", "result0161_22.nsv", "result0161_23.nsv", "result0161_24.nsv", "result0161_25.nsv", "result0161_26.nsv", "result0161_27.nsv", "result0161_28.nsv", "result0161_29.nsv", "result0161_30.nsv", "result0161_31.nsv", "result0161_32.nsv", "result0161_33.nsv", "result0161_34.nsv", "result0161_35.nsv"];
val thyn = "vfmTestDefs0161";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
