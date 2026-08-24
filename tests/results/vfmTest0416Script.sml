Theory vfmTest0416[no_sig_docs]
Ancestors vfmTestDefs0416
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0416_0.nsv", "result0416_1.nsv", "result0416_2.nsv", "result0416_3.nsv", "result0416_4.nsv", "result0416_5.nsv"];
val thyn = "vfmTestDefs0416";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
