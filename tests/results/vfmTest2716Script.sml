Theory vfmTest2716[no_sig_docs]
Ancestors vfmTestDefs2716
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2716_0.nsv", "result2716_1.nsv", "result2716_2.nsv", "result2716_3.nsv", "result2716_4.nsv", "result2716_5.nsv", "result2716_6.nsv", "result2716_7.nsv", "result2716_8.nsv", "result2716_9.nsv", "result2716_10.nsv", "result2716_11.nsv", "result2716_12.nsv", "result2716_13.nsv", "result2716_14.nsv", "result2716_15.nsv", "result2716_16.nsv", "result2716_17.nsv", "result2716_18.nsv", "result2716_19.nsv", "result2716_20.nsv", "result2716_21.nsv", "result2716_22.nsv", "result2716_23.nsv", "result2716_24.nsv", "result2716_25.nsv", "result2716_26.nsv", "result2716_27.nsv", "result2716_28.nsv", "result2716_29.nsv", "result2716_30.nsv", "result2716_31.nsv", "result2716_32.nsv", "result2716_33.nsv", "result2716_34.nsv", "result2716_35.nsv"];
val thyn = "vfmTestDefs2716";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
