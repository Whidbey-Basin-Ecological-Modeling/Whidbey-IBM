//
// Created by Troy Frever on 4/21/25.
//

#ifndef LOAD_UTILS_H
#define LOAD_UTILS_H

#include <netcdf>
#include <stdexcept>
#include <string>
#include "custom_exceptions.h"

class NcVarFillModeInterface {
public:
    virtual void getFillModeParameters(bool &fillActive, float *fillValue) const = 0;
    virtual void getFillModeParameters(bool &fillActive, int *fillValue) const = 0;

    virtual ~NcVarFillModeInterface() = default;
};

class NetCDFVarFillAdapter : public NcVarFillModeInterface {
public:
    NetCDFVarFillAdapter(const netCDF::NcVar &ncVar) : ncVar_(ncVar) {
    }

    void getFillModeParameters(bool &fillActive, float *fillValue) const override {
        const auto variableType = ncVar_.getType().getTypeClass();
        bool variableFillActive = false;
        ncVar_.getFillModeParameters(variableFillActive, static_cast<void *>(nullptr));
        fillActive = variableFillActive;

        if (fillValue == nullptr) {
            return;
        }

        switch (variableType) {
            case netCDF::NcType::nc_FLOAT: {
                float fileFillValue = NC_FILL_FLOAT;
                if (variableFillActive) {
                    ncVar_.getFillModeParameters(variableFillActive, static_cast<void *>(&fileFillValue));
                } else {
                    fileFillValue = getFillValueOrDefault(NC_FILL_FLOAT);
                }
                *fillValue = fileFillValue;
                return;
            }
            case netCDF::NcType::nc_DOUBLE: {
                double fileFillValue = NC_FILL_DOUBLE;
                if (variableFillActive) {
                    ncVar_.getFillModeParameters(variableFillActive, static_cast<void *>(&fileFillValue));
                } else {
                    fileFillValue = getFillValueOrDefault(static_cast<double>(NC_FILL_DOUBLE));
                }
                *fillValue = static_cast<float>(fileFillValue);
                return;
            }
            default:
                throw std::invalid_argument("Unsupported NetCDF type for float fill value: " + ncVar_.getType().getName());
        }
    }

    void getFillModeParameters(bool &fillActive, int *fillValue) const override {
        const auto variableType = ncVar_.getType().getTypeClass();
        if (variableType != netCDF::NcType::nc_INT) {
            throw std::invalid_argument("Unsupported NetCDF type for int fill value: " + ncVar_.getType().getName());
        }

        bool variableFillActive = false;
        ncVar_.getFillModeParameters(variableFillActive, static_cast<void *>(nullptr));
        fillActive = variableFillActive;

        if (fillValue == nullptr) {
            return;
        }

        int fileFillValue = NC_FILL_INT;
        if (variableFillActive) {
            ncVar_.getFillModeParameters(variableFillActive, static_cast<void *>(&fileFillValue));
        } else {
            fileFillValue = getFillValueOrDefault(NC_FILL_INT);
        }
        *fillValue = fileFillValue;
    }

private:
    template <typename T>
    T getFillValueOrDefault(T defaultValue) const {
        const auto attributes = ncVar_.getAtts();
        const auto fillValueAttribute = attributes.find("_FillValue");
        if (fillValueAttribute == attributes.end()) {
            return defaultValue;
        }
        if (fillValueAttribute->second.getAttLength() != 1) {
            throw std::invalid_argument("NetCDF _FillValue attribute must contain exactly one value");
        }

        T fillValue = defaultValue;
        fillValueAttribute->second.getValues(&fillValue);
        return fillValue;
    }

    const netCDF::NcVar &ncVar_;
};

bool is_missing_indicator(float value, float missing_indicator);
bool is_missing_indicator(int value, int missing_indicator);

bool fix_missing_value(float &cell, float &last_good_value, float missing_indicator);
/**
 * Validates that a value read from a NetCDF variable is not a missing/fill value.
 * Throws MissingRequiredValueException if the value matches the fill indicator.
 */
template <typename T>
void validate_required_value(const NcVarFillModeInterface &ncVar, T actual_value, std::string exception_msg) {
    bool is_fill_active;
    T missing_indicator;

    ncVar.getFillModeParameters(is_fill_active, &missing_indicator);
    if (is_missing_indicator(actual_value, missing_indicator)) {
        throw MissingRequiredValueException(exception_msg);
    }
}

float find_first_non_missing_value(const std::vector<float> &values, float missing_indicator);
void fix_all_missing_values(size_t stepCount, const NcVarFillModeInterface &nc_var_vector, std::vector<float> &hydro_vector,
                            const std::string &vector_name = "", std::vector<std
                                ::string> *error_log = nullptr);

#endif //LOAD_UTILS_H
