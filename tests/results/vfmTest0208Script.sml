Theory vfmTest0208[no_sig_docs]
Ancestors vfmTestDefs0208
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0208_0.nsv", "result0208_1.nsv", "result0208_2.nsv", "result0208_3.nsv", "result0208_4.nsv", "result0208_5.nsv", "result0208_6.nsv", "result0208_7.nsv", "result0208_8.nsv", "result0208_9.nsv", "result0208_10.nsv", "result0208_11.nsv", "result0208_12.nsv", "result0208_13.nsv", "result0208_14.nsv", "result0208_15.nsv", "result0208_16.nsv", "result0208_17.nsv", "result0208_18.nsv", "result0208_19.nsv", "result0208_20.nsv", "result0208_21.nsv", "result0208_22.nsv", "result0208_23.nsv", "result0208_24.nsv", "result0208_25.nsv", "result0208_26.nsv", "result0208_27.nsv", "result0208_28.nsv", "result0208_29.nsv", "result0208_30.nsv", "result0208_31.nsv"];
val thyn = "vfmTestDefs0208";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
