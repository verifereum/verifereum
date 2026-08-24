Theory vfmTest1946[no_sig_docs]
Ancestors vfmTestDefs1946
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1946_0.nsv", "result1946_1.nsv", "result1946_2.nsv", "result1946_3.nsv", "result1946_4.nsv", "result1946_5.nsv", "result1946_6.nsv", "result1946_7.nsv", "result1946_8.nsv", "result1946_9.nsv", "result1946_10.nsv", "result1946_11.nsv", "result1946_12.nsv", "result1946_13.nsv", "result1946_14.nsv", "result1946_15.nsv", "result1946_16.nsv", "result1946_17.nsv", "result1946_18.nsv", "result1946_19.nsv", "result1946_20.nsv", "result1946_21.nsv", "result1946_22.nsv", "result1946_23.nsv", "result1946_24.nsv", "result1946_25.nsv", "result1946_26.nsv", "result1946_27.nsv", "result1946_28.nsv", "result1946_29.nsv", "result1946_30.nsv", "result1946_31.nsv"];
val thyn = "vfmTestDefs1946";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
